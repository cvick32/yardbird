import {
  Link,
  Outlet,
  createRootRouteWithContext,
} from "@tanstack/react-router";
import { QueryClient } from "@tanstack/react-query";
import { AuthContext } from "../AuthProvider";

interface RouterContext {
  queryClient: QueryClient;
  auth: AuthContext;
}

export const Route = createRootRouteWithContext<RouterContext>()({
  component: RootComponent,
});

function RootComponent() {
  return (
    <>
      <div className="p-2 flex gap-2 bg-white">
        <div className="grow">
          <Link to="/" className="[&.active]:font-bold hover:underline">
            Index
          </Link>
        </div>
        <div>
          <Link to="/logout">Log Out</Link>
        </div>
      </div>
      <hr />
      <div className="m-2">
        <Outlet />
      </div>
    </>
  );
}
